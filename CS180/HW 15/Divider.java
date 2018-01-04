import java.util.concurrent.atomic.AtomicInteger;

/**
 * Created by Ryan on 10/27/2015.
 */
public class Divider extends Thread {
    int start = 0;
    int end = 0;
    private static AtomicInteger value = new AtomicInteger();

    Divider(int start, int end) {
        this.start = start;
        this.end = end;
    }

    public void inc() {
        value.getAndIncrement();
    }

    public void dec() {
        value.getAndDecrement();
    }

    public int get() {
        return value.get();
    }

    public void reset() {
        value.getAndSet(0);
    }

    public static int getCounter() {
        return value.get();
    }

    public static void setCounter() {
        value.getAndSet(0);
    }

    public void run() {
        for (int i = start; i < (end + 1); i++) {
            if (i % 7 == 0) {
                value.getAndIncrement();
            }
        }
    }
}
