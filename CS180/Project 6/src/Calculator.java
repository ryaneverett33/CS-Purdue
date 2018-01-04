import java.text.DecimalFormat;
import java.util.PriorityQueue;

public class Calculator {

	private CalculatorViewInterface view;
	
	String display = "";
    boolean canDigit;
    int currentOp;

    String displayCopy = "";
    boolean hasCopy = false;

    final int ADDOP = 1;    //currentOp
    final int SUBOP = 2;
    final int MULOP = 3;
    final int DIVOP = 4;
	/*
	 * Constructor. Initializes the instance variables.
	 */
	public Calculator(CalculatorViewInterface view) {
            this.view = view;
			view.display(display);
			canDigit = false;
			currentOp = -1;
	}
	public void inputDigit(char act) {
        //[0-9] or (+, -, /, *)
        if (hasCopy) {
            display = "";
            hasCopy = false;
        }
        char at = '?';
        if (display.length() != 0) at = display.charAt(display.length() - 1);
        boolean operator = false;
        if (at == '/' || at == '*' || at == '+' || at == '-') operator = true;
        if (operator) display = display + " ";
        if (act == '0' || act == '1' || act == '2' || act == '3' || act == '4' || act == '5') {
            display = display + act;
            view.display(display);
        }
        else if (act == '6' || act == '7' || act == '8' || act == '9') {
            display = display + act;
            view.display(display);
        }
        else {
            view.invalid();
        }
    }
    public void equal() {
        if (display.length() == 0) {
            view.invalid();
            return;
        }
        DecimalFormat df = new DecimalFormat("#.##");
        //If display contains a '/' or a '*'
        boolean mulDiv = display.contains("/") || display.contains("*");
        boolean addSub = display.contains("+") || display.contains("-");
        //Expression is already equal to itself, no evaluation required
        if (!mulDiv && !addSub) view.invalid();
        String[] lines = split();
        if (mulDiv || addSub) {
            displayCopy = display;
            hasCopy = true;
            char[] useless = display.toCharArray();
            for (int i = 0; i < useless.length; i++) {
                if (useless[i] == '/') currentOp = DIVOP;
                else if (useless[i] == '*') currentOp = MULOP;
                else if (useless[i] == '+') currentOp = ADDOP;
                else if (useless[i] == '-') currentOp = SUBOP;
            }
            //Check lines[]
            boolean isValid = isValid(lines);
            if (!isValid) {
                view.invalid();
                hasCopy = false;
                displayCopy = "";
                return;
            }
            double first = Double.parseDouble(lines[0]);
            double second = Double.parseDouble(lines[1]);
            if (currentOp == DIVOP) {
                double result = first / second;
                display = String.format("%.2f", result);
                view.display(display);
            }
            else if (currentOp == MULOP) {
                double result = first * second;
                display = String.format("%.2f", result);
                view.display(display);
            }
            else if (currentOp == ADDOP) {
                double result = first + second;
                display = String.format("%.2f", result);
                view.display(display);
            }
            else if (currentOp == SUBOP) {
                double result = first - second;
                display = String.format("%.2f", result);
                view.display(display);
            }
            else {
                view.invalid();
            }
        }
        /*if (!mulDiv && addSub) {
            //The most basic expression evaluation
            boolean found = false;
            boolean finished = false;
            double first = -200;
            double second = -200;
            int currentOp = -1;
            double result = -1000;
            hasCopy = true;
            displayCopy = display;
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
                            if (digits[i] == '+') currentOp = addOp;
                            else currentOp = subOp;
                            first = Double.parseDouble(lines[0]);
                        }
                        else {
                            //Do the operation
                            second = Double.parseDouble(lines[1]);
                            if (currentOp == addOp) result = first + second;
                            else result = first - second;
                            finished = true;
                        }
                    }
                    if (finished) {
                        //pass finished, set display and lines
                        int begin = lines[0].length() + 1 + lines[1].length();
                        display = Double.toString(result) + display.substring(begin, display.length());
                        lines = split();
                        break;
                    }
                }
            }
            while (found);
            display = Double.toString(result);
            view.display(display);
        }
        else if (!addSub && mulDiv) {
            //Lesser easy expression evaluation
        }
        else if (addSub && mulDiv){
            //Things become hard
        }
        else {
            view.invalid();
        }*/
    }
    public void dot() {
        //display = display + '.';
        //view.display(display);
        boolean hasOp = false;
        if (display.contains("/") || display.contains("*")) hasOp = true;
        else if (display.contains("+") || display.contains("-")) hasOp = true;
        if (hasOp) {
            String[] split = split();
            String line = split[split.length - 1];  //Get last string, use it for checking
            if (line.length() == 0) {
                display = display + ".";
                view.display(display);
            }
            else {
                if (line.contains(".")) {
                    view.invalid();
                    return;
                }
                else {
                    display = display + ".";
                    view.display(display);
                }
            }
        }
        else {
            //There are no operators in the display, consider as one double
            if (display.length() == 0) {
                display = display + ".";
                view.display(display);
            }
            else {
                if (display.contains(".")) {
                    //If it already contains a dot, disallow the add
                    view.invalid();
                    return;
                }
                else {
                    //Add the dot since it has not been used yet
                    display = display + ".";
                    view.display(display);
                }
            }
        }
    }
    public void delete() {
        if (display.length() == 0) {
            view.invalid();
            return;
        }
        char before = '?';
        if (display.length() >= 2) {
            before = display.charAt(display.length() - 2);
        }
        char last = display.charAt(display.length() - 1);
        boolean operator = false;
        if (last == '/') operator = true;
        else if (last == '*') operator = true;
        else if (last == '+') operator = true;
        else if (last == '-') operator = true;
        if (hasCopy) {
            display = displayCopy;
            view.display(display);
            hasCopy = false;
        }
        else if (!operator && before == ' ') {
            //+_2, remove _2
            display = display.substring(0, display.length() - 2);
            view.display(display);
        }
        else if (operator && before == ' ') {
            //2_+, remove _+
            display = display.substring(0, display.length() - 2);
            view.display(display);
        }
        else {
            display = display.substring(0, display.length() - 1);
            view.display(display);
        }
    }
    public void operator(char op) {
        if (display.length() == 0) {
            view.invalid();
            return;
        }
        int len = split().length;
        if (len> 1) {
            if (display.contains("/") || display.contains("*")) {
                view.invalid();
                return;
            }
            else if (display.contains("+") || display.contains("-")) {
                view.invalid();
                return;
            }
        }
        boolean matches = false;
        int index = -1;
        char[] pieces = display.toCharArray();
        for (int i = 0; i < pieces.length; i++) {
            if (pieces[i] == '/' || pieces[i] == '*') {
                index = i;
                matches = true;
            }
            else if (pieces[i] == '+' || pieces[i] == '-') {
                index = i;
                matches = true;
            }
        }
        if (matches) {
            //Last digit is an operator, replace it
            for (int i = 0; i < pieces.length; i++) {
                if (i == index) {
                    pieces[i] = op;
                    break;
                }
            }
            display = new String(pieces);
            view.display(display);
        }
        else {
            //Last digit is not an operator, add the operator
            display = display + " " + op;
            view.display(display);
        }
    }
    private String[] split() {
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
        return splitted;
    }
    private boolean isValid(String[] lines) {
        if (lines.length < 2) return false;
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].length() < 2) {
                return false;
            }
        }
        return true;
    }
}