class objectArrayTest {
    public static void main (String[] args) {
        System.out.println(new Tester().test());
    }
}
class Tester {
    A[] arr;
    public int test() {
        A a1;
        A a2;
        arr = new A[5];
        arr[0] = new A();
        arr[1] = new A();
        a1 = arr[0];
        a2 = arr[1];
        System.out.print(a1.setA(6));
        System.out.print(a2.setA(9));
        System.out.print(a1.getA());
        System.out.print(a2.getA());
        System.out.print("\n");
        return 80085;
    }
}
class A {
    int a;
    public int getA() {
        return a;
    }
    public int setA(int tmp) {
        a = tmp;
        return a;
    }
}