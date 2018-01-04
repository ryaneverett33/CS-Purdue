/**
 * Created by Ryan on 10/28/2015.
 */
public class Driver {
    public static void main(String[] args) {
        Thread a = new A();
        B b = new B();
        Thread b2 = new Thread(b);
        a.start();
        b2.start();
    }
}
