/**
 * Created by Ryan on 10/27/2015.
 */
import java.util.concurrent.atomic.AtomicInteger;
public class Divider extends Thread {
    int start = 0;
    int end = 0;

    Divider (int start, int end) {
        this.start = start;
        this.end = end;
    }
    public static Counter getCounter() {

    }
    public static void setCounter() {

    }

    public void run() {
        for (int i = start; i < (end+1); i++) {
            if (i % 7 == 0) {
                //Do magical code that adds number
            }
        }
    }
}
