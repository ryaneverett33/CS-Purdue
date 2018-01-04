/**
 * Created by Ryan on 10/28/2015.
 */
import java.util.concurrent.atomic.*;
public class Counter2 implements Counter {
    private AtomicInteger value = new AtomicInteger();

    public void inc() {
        value.getAndIncrement();
    }

    public void dec() {
        value.getAndDecrement();
    }

    public int get() {
        return value.get();
    }
}
