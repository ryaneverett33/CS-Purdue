/**
 * Created by Ryan on 12/1/2015.
 */
public class Test {
    public static void main(String[] args) {
        ResizableArray r = new ResizableArray();
        r.add(1);
        r.add(2);
        r.add(3);
        r.add(4);
        r.add(5);
        r.add(6);
        System.out.println(r.getSize()); //prints "6"
        System.out.println(r.getArraySize()); //prints "8"
        System.out.println(r.toString()); //prints "1,2,3,4,5,6,"
    }
}
