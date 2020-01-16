class storedObjectCall {
    public static void main (String[] args) {
        System.out.println(new A().test());
    }
}
class A {
    B b;
    public int test() {
        b = new B();
        return b.get();
    }
}
class B {
    int five;
    public int get() {
        five = 5;
        return five;
    }
}