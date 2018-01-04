/**
 * Created by Ryan on 10/27/2015.
 */
public class DividerCounter implements Counter {
    private int counter = 0;
    public synchronized void inc() {
        counter++;
    }
    public synchronized void dec() {
        counter--;
    }
    public int get() {
        return counter;
    }
}
