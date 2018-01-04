/**
 * Created by Ryan on 10/27/2015.
 */
public class DividerClient {
    public static void main(String[] args) {
        Counter counter = new DividerCounter();
        Thread t1 = new Thread(new Divider(1, 1000));
        Thread t2 = new Thread(new Divider(1001, 2000));
        Thread t3 = new Thread(new Divider(2001, 3000));
    }
}
