/**
 * Created by Ryan on 12/6/2015.
 */
public class tester implements CalculatorViewInterface {
    String display = "";
    boolean invalid = false;
    public void display(String display) {
        this.display = display;
    }
    public void invalid() {
        invalid = true;
    }
    public String getDisplay() { return this.display; }
    public boolean getInvalid() {
        if (!invalid) return false;
        else {
            invalid = false;
            return true;
        }
    }
}
